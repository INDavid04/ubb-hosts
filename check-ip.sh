# Nedelcu Alexandru-Constantin
#!/bin/bash

DNS_SERVER = $1

cat /etc/hosts | while IFS= read -r line; do
    if [[ "$ip" == \#* ]]; then
	break

    ip_file=$(echo "$line" | cut -d ' ' -f 1)
    name_file=$(echo "$line" | cut -d ' ' -f 2)

   
    if [[ "$name_file" == "localhost" || "$name_file" == "DESKTOP-PS905TO" ]]; then
        ip_lookup=$(nslookup "$name_file" | grep -m 1 'Address:' | tail -1 | cut -d ' ' -f 2)
    else
        ip_lookup=$(nslookup "$name_file" "$DNS_SERVER" | grep -m 1 'Address:' | tail -1 | cut -d ' ' -f 2)
    fi

 
    if [[ "$ip_nslookup" != "$ip_file" ]]; then
        echo "Bogus IP for $name_file in /etc/hosts!"
    fi
done
