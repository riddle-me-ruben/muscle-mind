# if these libraries do not work create a virtual enviornment and run this command in the terminal:
# pip install -r requirements.txt
import os
import pymysql
from flask import Flask, request, send_file, jsonify, redirect, url_for
from flask_mysqldb import MySQL
from dotenv import load_dotenv

# Load environment variables from the .env file (you need to place this file in the same folder you made for the project)
load_dotenv()

app = Flask(__name__)

# Database configuration (make sure .env file is in the same folder as app.py)
app.config['MYSQL_HOST'] = os.getenv('MYSQL_HOST')
app.config['MYSQL_USER'] = os.getenv('MYSQL_USER')
app.config['MYSQL_PASSWORD'] = os.getenv('MYSQL_PASSWORD')
app.config['MYSQL_DB'] = os.getenv('MYSQL_DB')
app.config['MYSQL_PORT'] = int(os.getenv('MYSQL_PORT'))

# Create a connection to the database
def get_db_connection():
    connection = pymysql.connect(
        host=app.config['MYSQL_HOST'],
        user=app.config['MYSQL_USER'],
        password=app.config['MYSQL_PASSWORD'],
        database=app.config['MYSQL_DB'],
        port=app.config['MYSQL_PORT']
    )
    return connection

# Serve the HTML file without using templates
@app.route('/')
def index():
    return send_file('/../client/index.html')

# Handle form submission
@app.route('/add_user', methods=['POST'])
def add_user():
    email = request.form['email']
    password = request.form['password']

    # Check if the email already exists
    connection = get_db_connection()
    cursor = connection.cursor()

    cursor.execute("SELECT * FROM users WHERE email = %s", (email,))
    existing_user = cursor.fetchone()

    if existing_user:
        print("Email already exists")
        cursor.close()
        connection.close()
        return redirect(url_for('index'))

    # If email does not exist, insert the new user
    cursor.execute("INSERT INTO users (email, password) VALUES (%s, %s)", (email, password))
    connection.commit()
    cursor.close()
    connection.close()

    return send_file('index.html')  # Send the HTML file again after adding the user

if __name__ == '__main__':
    app.run(debug=True)